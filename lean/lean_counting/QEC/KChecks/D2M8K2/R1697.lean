import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6788 = true := by
  decide +kernel

theorem tot6788 : totK PD2M8K2 D2M8K2.t6788 = [0, 115880449303, 445623158793, 321786313343, 32130353816, 0, 0, 0] := by
  decide +kernel

theorem rows6789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6789 = true := by
  decide +kernel

theorem tot6789 : totK PD2M8K2 D2M8K2.t6789 = [0, 0, 221408490525, 492161712251, 161405309271, 5218872685, 0, 0] := by
  decide +kernel

theorem rows6790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6790 = true := by
  decide +kernel

theorem tot6790 : totK PD2M8K2 D2M8K2.t6790 = [0, 173240819960, 433021000448, 293017762753, 35387074229, 0, 0, 0] := by
  decide +kernel

theorem rows6791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6791 = true := by
  decide +kernel

theorem tot6791 : totK PD2M8K2 D2M8K2.t6791 = [0, 155938437592, 465591706588, 259731110516, 18415189675, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
