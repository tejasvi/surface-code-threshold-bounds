import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2776 = true := by
  decide +kernel

theorem tot2776 : totK PD2M8K2 D2M8K2.t2776 = [0, 172941353536, 443945062383, 276850872262, 29676894246, 0, 0, 0] := by
  decide +kernel

theorem rows2777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2777 = true := by
  decide +kernel

theorem tot2777 : totK PD2M8K2 D2M8K2.t2777 = [0, 112776311510, 430845636946, 335756995931, 29727464663, 0, 0, 0] := by
  decide +kernel

theorem rows2778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2778 = true := by
  decide +kernel

theorem tot2778 : totK PD2M8K2 D2M8K2.t2778 = [0, 0, 212908864624, 493807926731, 174827877661, 4909780899, 0, 0] := by
  decide +kernel

theorem rows2779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2779 = true := by
  decide +kernel

theorem tot2779 : totK PD2M8K2 D2M8K2.t2779 = [0, 0, 190276672292, 461001170633, 219947420766, 17041558502, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
