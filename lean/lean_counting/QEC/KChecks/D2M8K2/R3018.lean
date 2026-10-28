import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12072 = true := by
  decide +kernel

theorem tot12072 : totK PD2M8K2 D2M8K2.t12072 = [0, 120174534136, 356395529810, 345028986112, 77159300768, 1227322468, 0, 0] := by
  decide +kernel

theorem rows12073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12073 = true := by
  decide +kernel

theorem tot12073 : totK PD2M8K2 D2M8K2.t12073 = [0, 163465894904, 448335918646, 282006428131, 30585669717, 0, 0, 0] := by
  decide +kernel

theorem rows12074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12074 = true := by
  decide +kernel

theorem tot12074 : totK PD2M8K2 D2M8K2.t12074 = [0, 136930472414, 441141679629, 284734311867, 22863830279, 0, 0, 0] := by
  decide +kernel

theorem rows12075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12075 = true := by
  decide +kernel

theorem tot12075 : totK PD2M8K2 D2M8K2.t12075 = [0, 0, 206066057816, 486356965217, 188884203513, 9642442870, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
