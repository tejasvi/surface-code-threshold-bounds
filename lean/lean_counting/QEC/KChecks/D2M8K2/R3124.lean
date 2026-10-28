import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12496 = true := by
  decide +kernel

theorem tot12496 : totK PD2M8K2 D2M8K2.t12496 = [0, 0, 171545747030, 445031198642, 237817431002, 18264884893, 0, 0] := by
  decide +kernel

theorem rows12497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12497 = true := by
  decide +kernel

theorem tot12497 : totK PD2M8K2 D2M8K2.t12497 = [0, 0, 208657231517, 495043546236, 188928323316, 5265834820, 0, 0] := by
  decide +kernel

theorem rows12498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12498 = true := by
  decide +kernel

theorem tot12498 : totK PD2M8K2 D2M8K2.t12498 = [0, 0, 188379479877, 485480217053, 188278092344, 5039544859, 0, 0] := by
  decide +kernel

theorem rows12499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12499 = true := by
  decide +kernel

theorem tot12499 : totK PD2M8K2 D2M8K2.t12499 = [0, 90905995700, 273973940744, 336812647505, 174436191652, 16298844657, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
