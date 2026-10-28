import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6276 = true := by
  decide +kernel

theorem tot6276 : totK PA10K2 A10K2.t6276 = [568469117275, 1989229212132, 1924372779282, 491765420412, 26374032118, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6277 = true := by
  decide +kernel

theorem tot6277 : totK PA10K2 A10K2.t6277 = [0, 702520071851, 2214871421422, 1860335125706, 373433706152, 13732569049, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6278 = true := by
  decide +kernel

theorem tot6278 : totK PA10K2 A10K2.t6278 = [0, 521821368165, 1829055620584, 1911466284306, 629750943877, 48929425941, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6279 = true := by
  decide +kernel

theorem tot6279 : totK PA10K2 A10K2.t6279 = [0, 431013620559, 1752006287793, 1978338375993, 547683560380, 32523532663, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
