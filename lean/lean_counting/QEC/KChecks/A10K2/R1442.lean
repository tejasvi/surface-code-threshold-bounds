import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5768 = true := by
  decide +kernel

theorem tot5768 : totK PA10K2 A10K2.t5768 = [0, 0, 0, 550165624721, 1828133747558, 1763252142393, 476437811907, 31690783744, 0, 0] := by
  decide +kernel

theorem rows5769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5769 = true := by
  decide +kernel

theorem tot5769 : totK PA10K2 A10K2.t5769 = [0, 0, 0, 430962416020, 1658698920593, 1837356785404, 553955732498, 50109395967, 0, 0] := by
  decide +kernel

theorem rows5770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5770 = true := by
  decide +kernel

theorem tot5770 : totK PA10K2 A10K2.t5770 = [0, 0, 0, 301644132046, 1568300381063, 2008717263188, 660383769133, 51971636734, 0, 0] := by
  decide +kernel

theorem rows5771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5771 = true := by
  decide +kernel

theorem tot5771 : totK PA10K2 A10K2.t5771 = [0, 0, 319364639558, 905595250647, 954705411571, 1296138159085, 992595140842, 213642913445, 6354482628, 0] := by
  decide +kernel

end QECKChecks.A10K2
