import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5284 = true := by
  decide +kernel

theorem tot5284 : totK PD2M8K2 D2M8K2.t5284 = [0, 171490899704, 461329290326, 259400624863, 18737575145, 0, 0, 0] := by
  decide +kernel

theorem rows5285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5285 = true := by
  decide +kernel

theorem tot5285 : totK PD2M8K2 D2M8K2.t5285 = [0, 0, 245544046677, 509371050871, 140731619169, 2309606161, 0, 0] := by
  decide +kernel

theorem rows5286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5286 = true := by
  decide +kernel

theorem tot5286 : totK PD2M8K2 D2M8K2.t5286 = [0, 66625207258, 272497743191, 388357814479, 143461803451, 10740121073, 0, 0] := by
  decide +kernel

theorem rows5287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5287 = true := by
  decide +kernel

theorem tot5287 : totK PD2M8K2 D2M8K2.t5287 = [0, 174094303300, 459316993833, 265507235004, 24404469341, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
