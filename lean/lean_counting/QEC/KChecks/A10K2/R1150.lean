import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4600 = true := by
  decide +kernel

theorem tot4600 : totK PA10K2 A10K2.t4600 = [0, 579480951836, 2076139297618, 1990166907027, 455711558246, 13814447077, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4601 = true := by
  decide +kernel

theorem tot4601 : totK PA10K2 A10K2.t4601 = [0, 422312806027, 1674486454045, 2021136674965, 760749006613, 69753583762, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4602 = true := by
  decide +kernel

theorem tot4602 : totK PA10K2 A10K2.t4602 = [0, 528087305681, 1930200534953, 1955271071764, 449921012604, 11933990244, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4603 = true := by
  decide +kernel

theorem tot4603 : totK PA10K2 A10K2.t4603 = [0, 0, 617958404504, 1995565408143, 1683249900066, 398031249958, 25565504801, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
