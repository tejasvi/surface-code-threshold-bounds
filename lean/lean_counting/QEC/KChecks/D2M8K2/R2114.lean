import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8456 = true := by
  decide +kernel

theorem tot8456 : totK PD2M8K2 D2M8K2.t8456 = [0, 182586849334, 437346730318, 265381463420, 30322938706, 0, 0, 0] := by
  decide +kernel

theorem rows8457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8457 = true := by
  decide +kernel

theorem tot8457 : totK PD2M8K2 D2M8K2.t8457 = [0, 120476991143, 441742181678, 321473692434, 31893859244, 0, 0, 0] := by
  decide +kernel

theorem rows8458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8458 = true := by
  decide +kernel

theorem tot8458 : totK PD2M8K2 D2M8K2.t8458 = [0, 36923124222, 285576384558, 474941944402, 112944304700, 1409560813, 0, 0] := by
  decide +kernel

theorem rows8459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8459 = true := by
  decide +kernel

theorem tot8459 : totK PD2M8K2 D2M8K2.t8459 = [0, 198511658685, 462695553941, 223441566707, 18290608745, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
