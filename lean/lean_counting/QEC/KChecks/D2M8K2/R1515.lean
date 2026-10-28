import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6060 = true := by
  decide +kernel

theorem tot6060 : totK PD2M8K2 D2M8K2.t6060 = [0, 180823914976, 428234976174, 278867138162, 35624166303, 0, 0, 0] := by
  decide +kernel

theorem rows6061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6061 = true := by
  decide +kernel

theorem tot6061 : totK PD2M8K2 D2M8K2.t6061 = [0, 174527105135, 464194513843, 243601872642, 16714091490, 0, 0, 0] := by
  decide +kernel

theorem rows6062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6062 = true := by
  decide +kernel

theorem tot6062 : totK PD2M8K2 D2M8K2.t6062 = [0, 73213873603, 334741507707, 362733450799, 125356527925, 15863492353, 0, 0] := by
  decide +kernel

theorem rows6063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6063 = true := by
  decide +kernel

theorem tot6063 : totK PD2M8K2 D2M8K2.t6063 = [0, 0, 172568458538, 457744839239, 241298650926, 13527618342, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
