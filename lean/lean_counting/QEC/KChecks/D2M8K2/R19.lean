import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows76 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t76 = true := by
  decide +kernel

theorem tot76 : totK PD2M8K2 D2M8K2.t76 = [191619907270, 470367426704, 244404857108, 20890728607, 0, 0, 0, 0] := by
  decide +kernel

theorem rows77 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t77 = true := by
  decide +kernel

theorem tot77 : totK PD2M8K2 D2M8K2.t77 = [192815900482, 476929675834, 224052656859, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows78 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t78 = true := by
  decide +kernel

theorem tot78 : totK PD2M8K2 D2M8K2.t78 = [19434652667, 304898280906, 471185470542, 100564218337, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows79 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t79 = true := by
  decide +kernel

theorem tot79 : totK PD2M8K2 D2M8K2.t79 = [0, 203928110867, 474559324651, 190815141899, 12052611869, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
