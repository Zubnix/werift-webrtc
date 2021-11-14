/* eslint-disable @typescript-eslint/ban-ts-comment */
import "buffer";
import { Red } from "werift-rtp";
import { peer, sleep } from "../fixture";

fdescribe("mediachannel_rtx", () => {
  const label = "mediachannel_red_client_answer";
  it(
    label,
    async () =>
      new Promise<void>(async (done) => {
        const receiverTransform = (receiver: RTCRtpReceiver) => {
          console.warn("start receiverTransform");
          const receiverStreams = (receiver as any).createEncodedStreams();
          const readableStream = receiverStreams.readable;
          const writableStream = receiverStreams.writable;
          const transformStream = new TransformStream({
            transform: (encodedFrame, controller) => {
              const data = encodedFrame.data;
              const red = Red.deSerialize(Buffer.from(data));
              console.log(red);
              expect(red.payloads.length).toBe(2);
              controller.enqueue(encodedFrame);
              done();
            },
          });
          readableStream.pipeThrough(transformStream).pipeTo(writableStream);
        };

        if (!peer.connected) await new Promise<void>((r) => peer.on("open", r));
        await sleep(100);

        const pc = new RTCPeerConnection({
          //@ts-ignore
          encodedInsertableStreams: true,
          iceServers: [{ urls: "stun:stun.l.google.com:19302" }],
        });
        pc.onicecandidate = ({ candidate }) => {
          peer
            .request(label, {
              type: "candidate",
              payload: candidate,
            })
            .catch(() => {});
        };
        pc.ontrack = async (ev) => {
          const receiver = ev.receiver;
          receiverTransform(receiver);
        };

        const offer = await peer.request(label, {
          type: "init",
        });
        await pc.setRemoteDescription(offer);
        await pc.setLocalDescription(await pc.createAnswer());

        peer
          .request(label, {
            type: "answer",
            payload: pc.localDescription,
          })
          .catch(() => {});
      }),
    10 * 1000
  );
});
