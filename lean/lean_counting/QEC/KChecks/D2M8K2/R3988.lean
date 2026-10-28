import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15952 = true := by
  decide +kernel

theorem tot15952 : totK PD2M8K2 D2M8K2.t15952 = [0, 0, 123649510987, 339180027802, 289193510236, 130092594910, 13326740810, 0] := by
  decide +kernel

theorem rows15953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15953 = true := by
  decide +kernel

theorem tot15953 : totK PD2M8K2 D2M8K2.t15953 = [0, 0, 180141976008, 453978837339, 227119625809, 13825518948, 0, 0] := by
  decide +kernel

theorem rows15954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15954 = true := by
  decide +kernel

theorem tot15954 : totK PD2M8K2 D2M8K2.t15954 = [0, 0, 124655673597, 432125265167, 305605745451, 27832716110, 0, 0] := by
  decide +kernel

theorem rows15955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15955 = true := by
  decide +kernel

theorem tot15955 : totK PD2M8K2 D2M8K2.t15955 = [0, 0, 0, 274769295368, 512884257360, 99040747300, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
