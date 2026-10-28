import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15004 = true := by
  decide +kernel

theorem tot15004 : totK PD2M8K2 D2M8K2.t15004 = [0, 193478841990, 457598532660, 245324842544, 22743924844, 0, 0, 0] := by
  decide +kernel

theorem rows15005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15005 = true := by
  decide +kernel

theorem tot15005 : totK PD2M8K2 D2M8K2.t15005 = [0, 189493684010, 474114512684, 226695200431, 12423165040, 0, 0, 0] := by
  decide +kernel

theorem rows15006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15006 = true := by
  decide +kernel

theorem tot15006 : totK PD2M8K2 D2M8K2.t15006 = [0, 38150555787, 317810868935, 446499378489, 95599616612, 1198073392, 0, 0] := by
  decide +kernel

theorem rows15007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15007 = true := by
  decide +kernel

theorem tot15007 : totK PD2M8K2 D2M8K2.t15007 = [0, 0, 202656601536, 463036362568, 192550471440, 11991925116, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
