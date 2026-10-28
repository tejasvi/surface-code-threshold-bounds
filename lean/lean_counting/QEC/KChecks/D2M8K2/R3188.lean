import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12752 = true := by
  decide +kernel

theorem tot12752 : totK PD2M8K2 D2M8K2.t12752 = [0, 0, 142016462787, 385656602629, 314142501609, 80267856336, 1415142070, 0] := by
  decide +kernel

theorem rows12753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12753 = true := by
  decide +kernel

theorem tot12753 : totK PD2M8K2 D2M8K2.t12753 = [0, 0, 174133343930, 455829309752, 251215409471, 15105098132, 0, 0] := by
  decide +kernel

theorem rows12754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12754 = true := by
  decide +kernel

theorem tot12754 : totK PD2M8K2 D2M8K2.t12754 = [0, 0, 84786226771, 422726499814, 365003456479, 47722491922, 0, 0] := by
  decide +kernel

theorem rows12755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12755 = true := by
  decide +kernel

theorem tot12755 : totK PD2M8K2 D2M8K2.t12755 = [0, 0, 0, 203573931930, 516922871544, 152802159490, 2484078857, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
