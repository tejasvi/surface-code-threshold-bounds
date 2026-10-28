import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12216 = true := by
  decide +kernel

theorem tot12216 : totK PD2M8K2 D2M8K2.t12216 = [0, 326385857662, 520437489826, 82806658689, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12217 = true := by
  decide +kernel

theorem tot12217 : totK PD2M8K2 D2M8K2.t12217 = [155484015133, 347189311910, 316917456255, 98113004402, 3880716147, 0, 0, 0] := by
  decide +kernel

theorem rows12218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12218 = true := by
  decide +kernel

theorem tot12218 : totK PD2M8K2 D2M8K2.t12218 = [174544416507, 469143216970, 244784935702, 16650676461, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12219 = true := by
  decide +kernel

theorem tot12219 : totK PD2M8K2 D2M8K2.t12219 = [0, 269688897626, 486917275430, 135077948255, 3681172965, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
