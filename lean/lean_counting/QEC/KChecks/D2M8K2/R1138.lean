import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4552 = true := by
  decide +kernel

theorem tot4552 : totK PD2M8K2 D2M8K2.t4552 = [0, 0, 201031322919, 483905818795, 218551954742, 9424143550, 0, 0] := by
  decide +kernel

theorem rows4553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4553 = true := by
  decide +kernel

theorem tot4553 : totK PD2M8K2 D2M8K2.t4553 = [0, 0, 26315000935, 269803976830, 413258092552, 187825416444, 21400436502, 0] := by
  decide +kernel

theorem rows4554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4554 = true := by
  decide +kernel

theorem tot4554 : totK PD2M8K2 D2M8K2.t4554 = [0, 0, 0, 204946774277, 485192984380, 199970487134, 7928356585, 0] := by
  decide +kernel

theorem rows4555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4555 = true := by
  decide +kernel

theorem tot4555 : totK PD2M8K2 D2M8K2.t4555 = [0, 0, 69708644312, 252835965269, 381489215086, 175791140947, 8170814383, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
