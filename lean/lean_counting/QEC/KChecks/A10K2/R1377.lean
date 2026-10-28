import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5508 = true := by
  decide +kernel

theorem tot5508 : totK PA10K2 A10K2.t5508 = [0, 0, 0, 618029805717, 2033291134564, 1679615524792, 359389292119, 25336174642, 0, 0] := by
  decide +kernel

theorem rows5509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5509 = true := by
  decide +kernel

theorem tot5509 : totK PA10K2 A10K2.t5509 = [0, 0, 0, 539561062661, 1802316854761, 1770332858821, 468095511088, 31009878902, 0, 0] := by
  decide +kernel

theorem rows5510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5510 = true := by
  decide +kernel

theorem tot5510 : totK PA10K2 A10K2.t5510 = [0, 0, 0, 466179142761, 1794521262430, 1867887268244, 455760989027, 25454126167, 0, 0] := by
  decide +kernel

theorem rows5511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5511 = true := by
  decide +kernel

theorem tot5511 : totK PA10K2 A10K2.t5511 = [0, 0, 0, 0, 804932058593, 2167354451917, 1334673125338, 174073996660, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
