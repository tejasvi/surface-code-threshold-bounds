import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1700 = true := by
  decide +kernel

theorem tot1700 : totK PA10K2 A10K2.t1700 = [0, 0, 0, 676239022486, 2145298039546, 1539929671431, 261986827965, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1701 = true := by
  decide +kernel

theorem tot1701 : totK PA10K2 A10K2.t1701 = [0, 0, 0, 461711149265, 1769227734358, 1868815619087, 488810069855, 31193351345, 0, 0] := by
  decide +kernel

theorem rows1702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1702 = true := by
  decide +kernel

theorem tot1702 : totK PA10K2 A10K2.t1702 = [0, 0, 0, 629746299764, 2021225673647, 1614146328200, 347160507357, 25336174642, 0, 0] := by
  decide +kernel

theorem rows1703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1703 = true := by
  decide +kernel

theorem tot1703 : totK PA10K2 A10K2.t1703 = [0, 0, 0, 503091937278, 1777586114313, 1759170586984, 475670279699, 31009878902, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
