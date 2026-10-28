import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5620 = true := by
  decide +kernel

theorem tot5620 : totK PA10K2 A10K2.t5620 = [0, 0, 277188877889, 1183549699618, 1873417251233, 1151523269797, 193703612551, 6034215561, 0, 0] := by
  decide +kernel

theorem rows5621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5621 = true := by
  decide +kernel

theorem tot5621 : totK PA10K2 A10K2.t5621 = [0, 0, 542356940553, 1887369312622, 1791363324366, 424673130081, 25756277031, 0, 0, 0] := by
  decide +kernel

theorem rows5622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5622 = true := by
  decide +kernel

theorem tot5622 : totK PA10K2 A10K2.t5622 = [0, 0, 0, 925613094413, 2389318419437, 1221177122142, 106331449930, 0, 0, 0] := by
  decide +kernel

theorem rows5623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5623 = true := by
  decide +kernel

theorem tot5623 : totK PA10K2 A10K2.t5623 = [0, 0, 0, 471098373983, 1819154394507, 1894976433199, 504337119232, 31987755669, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
