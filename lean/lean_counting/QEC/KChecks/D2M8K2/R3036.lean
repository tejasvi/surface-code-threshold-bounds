import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12144 = true := by
  decide +kernel

theorem tot12144 : totK PD2M8K2 D2M8K2.t12144 = [0, 0, 235488127999, 496721846666, 152925419154, 2895580614, 0, 0] := by
  decide +kernel

theorem rows12145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12145 = true := by
  decide +kernel

theorem tot12145 : totK PD2M8K2 D2M8K2.t12145 = [0, 0, 256521149408, 476293712873, 142483480922, 4598458179, 0, 0] := by
  decide +kernel

theorem rows12146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12146 = true := by
  decide +kernel

theorem tot12146 : totK PD2M8K2 D2M8K2.t12146 = [0, 0, 169262496297, 472087247213, 218608690623, 13670760027, 0, 0] := by
  decide +kernel

theorem rows12147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12147 = true := by
  decide +kernel

theorem tot12147 : totK PD2M8K2 D2M8K2.t12147 = [0, 0, 188655600801, 468652627445, 221393908201, 12443528988, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
