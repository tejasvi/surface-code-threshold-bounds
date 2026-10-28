import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3920 = true := by
  decide +kernel

theorem tot3920 : totK PD2M8K2 D2M8K2.t3920 = [0, 0, 185916430526, 510046284167, 199366801304, 3841667060, 0, 0] := by
  decide +kernel

theorem rows3921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3921 = true := by
  decide +kernel

theorem tot3921 : totK PD2M8K2 D2M8K2.t3921 = [0, 173281589747, 425793282136, 239073548853, 60250109630, 5593966081, 0, 0] := by
  decide +kernel

theorem rows3922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3922 = true := by
  decide +kernel

theorem tot3922 : totK PD2M8K2 D2M8K2.t3922 = [0, 179195793275, 461038974093, 241760162932, 16706214026, 0, 0, 0] := by
  decide +kernel

theorem rows3923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3923 = true := by
  decide +kernel

theorem tot3923 : totK PD2M8K2 D2M8K2.t3923 = [0, 85381448563, 345432750923, 381760498364, 84632950258, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
