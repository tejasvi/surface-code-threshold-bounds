import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2072 = true := by
  decide +kernel

theorem tot2072 : totK PD2M8K2 D2M8K2.t2072 = [0, 193290754591, 453478944485, 230361085232, 17075945103, 0, 0, 0] := by
  decide +kernel

theorem rows2073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2073 = true := by
  decide +kernel

theorem tot2073 : totK PD2M8K2 D2M8K2.t2073 = [0, 109961431301, 429849660480, 327023903542, 31238449321, 0, 0, 0] := by
  decide +kernel

theorem rows2074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2074 = true := by
  decide +kernel

theorem tot2074 : totK PD2M8K2 D2M8K2.t2074 = [0, 0, 270438317196, 509929302092, 113249760464, 1369150432, 0, 0] := by
  decide +kernel

theorem rows2075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2075 = true := by
  decide +kernel

theorem tot2075 : totK PD2M8K2 D2M8K2.t2075 = [0, 157857407050, 425983150842, 302980122084, 35929593239, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
