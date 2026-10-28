import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1776 = true := by
  decide +kernel

theorem tot1776 : totK PA10K2 A10K2.t1776 = [0, 0, 0, 280701655614, 1203039107341, 1945842200336, 1088030593158, 174361211873, 5546304973, 0] := by
  decide +kernel

theorem rows1777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1777 = true := by
  decide +kernel

theorem tot1777 : totK PA10K2 A10K2.t1777 = [0, 0, 304031809754, 1241124499570, 1949615346952, 1286069058708, 239574963477, 6782479114, 0, 0] := by
  decide +kernel

theorem rows1778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1778 = true := by
  decide +kernel

theorem tot1778 : totK PA10K2 A10K2.t1778 = [0, 0, 459942519120, 1813065731841, 2024545900326, 630954039198, 31049444317, 0, 0, 0] := by
  decide +kernel

theorem rows1779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1779 = true := by
  decide +kernel

theorem tot1779 : totK PA10K2 A10K2.t1779 = [0, 0, 0, 529762952359, 1958963038634, 1804101873219, 376955543160, 25734533292, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
