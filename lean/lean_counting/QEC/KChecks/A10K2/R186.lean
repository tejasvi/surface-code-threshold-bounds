import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t744 = true := by
  decide +kernel

theorem tot744 : totK PA10K2 A10K2.t744 = [0, 925335572295, 2390952035457, 1282104559919, 113579504810, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t745 = true := by
  decide +kernel

theorem tot745 : totK PA10K2 A10K2.t745 = [0, 468997704994, 1789647130223, 1970374329467, 550669349442, 31987755669, 0, 0, 0, 0] := by
  decide +kernel

theorem rows746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t746 = true := by
  decide +kernel

theorem tot746 : totK PA10K2 A10K2.t746 = [0, 587040362597, 2045283234998, 1881917579192, 430359002326, 13149912228, 0, 0, 0, 0] := by
  decide +kernel

theorem rows747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t747 = true := by
  decide +kernel

theorem tot747 : totK PA10K2 A10K2.t747 = [0, 460248007464, 1718148330013, 1877413562048, 570914049435, 50267370225, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
