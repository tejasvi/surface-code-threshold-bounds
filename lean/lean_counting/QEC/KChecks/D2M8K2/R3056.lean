import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12224 = true := by
  decide +kernel

theorem tot12224 : totK PD2M8K2 D2M8K2.t12224 = [0, 0, 173697139218, 491984277553, 210663508986, 7658844075, 0, 0] := by
  decide +kernel

theorem rows12225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12225 = true := by
  decide +kernel

theorem tot12225 : totK PD2M8K2 D2M8K2.t12225 = [0, 113125941864, 319129531912, 310501550769, 136028688130, 7877424857, 0, 0] := by
  decide +kernel

theorem rows12226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12226 = true := by
  decide +kernel

theorem tot12226 : totK PD2M8K2 D2M8K2.t12226 = [0, 165690972018, 442306112748, 276344550835, 30347703461, 0, 0, 0] := by
  decide +kernel

theorem rows12227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12227 = true := by
  decide +kernel

theorem tot12227 : totK PD2M8K2 D2M8K2.t12227 = [0, 130399076471, 444868780940, 292531953150, 18593080616, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
