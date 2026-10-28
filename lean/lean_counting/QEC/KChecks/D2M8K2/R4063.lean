import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16252 = true := by
  decide +kernel

theorem tot16252 : totK PD2M8K2 D2M8K2.t16252 = [0, 0, 173778624724, 445950555458, 256354873991, 23963695312, 0, 0] := by
  decide +kernel

theorem rows16253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16253 = true := by
  decide +kernel

theorem tot16253 : totK PD2M8K2 D2M8K2.t16253 = [0, 0, 92937627352, 405139492463, 371590497155, 39001182780, 0, 0] := by
  decide +kernel

theorem rows16254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16254 = true := by
  decide +kernel

theorem tot16254 : totK PD2M8K2 D2M8K2.t16254 = [0, 0, 0, 213055996976, 487285304934, 169647493254, 4901932702, 0] := by
  decide +kernel

theorem rows16255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16255 = true := by
  decide +kernel

theorem tot16255 : totK PD2M8K2 D2M8K2.t16255 = [0, 0, 0, 194495492266, 459233421929, 211933009606, 17014456371, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
