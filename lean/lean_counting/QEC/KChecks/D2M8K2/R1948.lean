import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7792 = true := by
  decide +kernel

theorem tot7792 : totK PD2M8K2 D2M8K2.t7792 = [0, 176407831322, 438384108095, 253320142412, 25990246889, 0, 0, 0] := by
  decide +kernel

theorem rows7793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7793 = true := by
  decide +kernel

theorem tot7793 : totK PD2M8K2 D2M8K2.t7793 = [0, 137960552653, 445304422244, 283499025466, 23634285059, 0, 0, 0] := by
  decide +kernel

theorem rows7794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7794 = true := by
  decide +kernel

theorem tot7794 : totK PD2M8K2 D2M8K2.t7794 = [0, 0, 286857226496, 509485021097, 99213805237, 1096505104, 0, 0] := by
  decide +kernel

theorem rows7795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7795 = true := by
  decide +kernel

theorem tot7795 : totK PD2M8K2 D2M8K2.t7795 = [0, 138155694125, 355160281592, 307102761184, 91569777096, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
