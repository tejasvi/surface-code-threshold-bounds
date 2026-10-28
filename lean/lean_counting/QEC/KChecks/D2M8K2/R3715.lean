import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14860 = true := by
  decide +kernel

theorem tot14860 : totK PD2M8K2 D2M8K2.t14860 = [0, 0, 296636879749, 481823437263, 82609766285, 1239866073, 0, 0] := by
  decide +kernel

theorem rows14861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14861 = true := by
  decide +kernel

theorem tot14861 : totK PD2M8K2 D2M8K2.t14861 = [0, 165875177043, 438693249101, 290001551503, 30876070581, 0, 0, 0] := by
  decide +kernel

theorem rows14862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14862 = true := by
  decide +kernel

theorem tot14862 : totK PD2M8K2 D2M8K2.t14862 = [0, 203933908955, 484559091022, 211839314828, 11122924523, 0, 0, 0] := by
  decide +kernel

theorem rows14863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14863 = true := by
  decide +kernel

theorem tot14863 : totK PD2M8K2 D2M8K2.t14863 = [0, 192421006263, 474756940650, 219292123867, 12900833004, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
