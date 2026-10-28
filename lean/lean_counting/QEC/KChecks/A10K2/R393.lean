import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1572 = true := by
  decide +kernel

theorem tot1572 : totK PA10K2 A10K2.t1572 = [0, 0, 304573652302, 1206213597921, 1804724979688, 1262310681151, 359465362598, 29010686974, 0, 0] := by
  decide +kernel

theorem rows1573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1573 = true := by
  decide +kernel

theorem tot1573 : totK PA10K2 A10K2.t1573 = [0, 0, 482130463350, 1823120880994, 1996610340989, 609549164702, 35698002757, 0, 0, 0] := by
  decide +kernel

theorem rows1574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1574 = true := by
  decide +kernel

theorem tot1574 : totK PA10K2 A10K2.t1574 = [0, 0, 0, 564234510973, 1989584220786, 1735588442754, 401315855315, 25371180993, 0, 0] := by
  decide +kernel

theorem rows1575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1575 = true := by
  decide +kernel

theorem tot1575 : totK PA10K2 A10K2.t1575 = [0, 0, 410191170018, 1473437581290, 1809966091439, 896613222675, 160010653880, 5460492893, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
