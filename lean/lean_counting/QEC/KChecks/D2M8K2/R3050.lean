import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12200 = true := by
  decide +kernel

theorem tot12200 : totK PD2M8K2 D2M8K2.t12200 = [127234728902, 324876333858, 323774019879, 136424702659, 13468148062, 0, 0, 0] := by
  decide +kernel

theorem rows12201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12201 = true := by
  decide +kernel

theorem tot12201 : totK PD2M8K2 D2M8K2.t12201 = [191452129492, 463690902240, 239686923611, 16630841668, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12202 = true := by
  decide +kernel

theorem tot12202 : totK PD2M8K2 D2M8K2.t12202 = [125185423002, 446974845934, 310520212380, 34843634392, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12203 = true := by
  decide +kernel

theorem tot12203 : totK PD2M8K2 D2M8K2.t12203 = [0, 173110634023, 448234052298, 260312743026, 25373788367, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
