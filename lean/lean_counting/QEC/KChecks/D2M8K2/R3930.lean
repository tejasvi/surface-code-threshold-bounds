import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15720 = true := by
  decide +kernel

theorem tot15720 : totK PD2M8K2 D2M8K2.t15720 = [0, 0, 15921317223, 324351466540, 498403813261, 55653688543, 0, 0] := by
  decide +kernel

theorem rows15721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15721 = true := by
  decide +kernel

theorem tot15721 : totK PD2M8K2 D2M8K2.t15721 = [0, 0, 166333448552, 447946433587, 279047622946, 30232670057, 0, 0] := by
  decide +kernel

theorem rows15722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15722 = true := by
  decide +kernel

theorem tot15722 : totK PD2M8K2 D2M8K2.t15722 = [0, 0, 237517231656, 508027882155, 167905578027, 3834552406, 0, 0] := by
  decide +kernel

theorem rows15723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15723 = true := by
  decide +kernel

theorem tot15723 : totK PD2M8K2 D2M8K2.t15723 = [0, 0, 0, 256383267960, 488261655758, 158225109647, 10165445843, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
