import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5820 = true := by
  decide +kernel

theorem tot5820 : totK PA10K2 A10K2.t5820 = [0, 0, 449418711251, 1782019962395, 1997123545402, 581866169995, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows5821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5821 = true := by
  decide +kernel

theorem tot5821 : totK PA10K2 A10K2.t5821 = [0, 0, 155477502832, 980303363850, 1958414394180, 1439638568917, 329786107515, 25734533292, 0, 0] := by
  decide +kernel

theorem rows5822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5822 = true := by
  decide +kernel

theorem tot5822 : totK PA10K2 A10K2.t5822 = [0, 0, 230347244795, 1071067204511, 1843998398584, 1332424805128, 216652532592, 6034215561, 0, 0] := by
  decide +kernel

theorem rows5823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5823 = true := by
  decide +kernel

theorem tot5823 : totK PA10K2 A10K2.t5823 = [0, 0, 471098579951, 1656329374919, 1889942002815, 664328529222, 52232171148, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
