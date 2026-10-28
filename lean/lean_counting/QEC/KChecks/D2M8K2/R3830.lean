import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15320 = true := by
  decide +kernel

theorem tot15320 : totK PD2M8K2 D2M8K2.t15320 = [0, 0, 134454169485, 426876040460, 324370777562, 31377530922, 0, 0] := by
  decide +kernel

theorem rows15321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15321 = true := by
  decide +kernel

theorem tot15321 : totK PD2M8K2 D2M8K2.t15321 = [0, 0, 178755760610, 449717420018, 263131682139, 24325835936, 0, 0] := by
  decide +kernel

theorem rows15322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15322 = true := by
  decide +kernel

theorem tot15322 : totK PD2M8K2 D2M8K2.t15322 = [0, 0, 99143845592, 399648488684, 345539858321, 47267477456, 1162515529, 0] := by
  decide +kernel

theorem rows15323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15323 = true := by
  decide +kernel

theorem tot15323 : totK PD2M8K2 D2M8K2.t15323 = [0, 0, 0, 247167012625, 512132973784, 129895855189, 4030866388, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
