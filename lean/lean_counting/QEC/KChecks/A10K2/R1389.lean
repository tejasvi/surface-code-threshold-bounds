import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5556 = true := by
  decide +kernel

theorem tot5556 : totK PA10K2 A10K2.t5556 = [0, 0, 575679818280, 1681960204899, 1575056142658, 879465233805, 331054600008, 32670088203, 0, 0] := by
  decide +kernel

theorem rows5557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5557 = true := by
  decide +kernel

theorem tot5557 : totK PA10K2 A10K2.t5557 = [0, 0, 17057514467, 874406545497, 2302630959966, 1588346636687, 272552516695, 7685602490, 0, 0] := by
  decide +kernel

theorem rows5558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5558 = true := by
  decide +kernel

theorem tot5558 : totK PA10K2 A10K2.t5558 = [0, 0, 463631794208, 1659255247872, 1978079499746, 788356173882, 71751729091, 0, 0, 0] := by
  decide +kernel

theorem rows5559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5559 = true := by
  decide +kernel

theorem tot5559 : totK PA10K2 A10K2.t5559 = [0, 0, 306418931549, 1605535583225, 2180541504673, 843295821248, 72197922044, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
