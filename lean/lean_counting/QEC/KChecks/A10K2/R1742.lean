import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6968 = true := by
  decide +kernel

theorem tot6968 : totK PA10K2 A10K2.t6968 = [0, 244406495887, 1353911521170, 2165299266438, 1109723891965, 121788100172, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6969 = true := by
  decide +kernel

theorem tot6969 : totK PA10K2 A10K2.t6969 = [0, 0, 613668236608, 2067936691728, 1924502577383, 431634406877, 13816090359, 0, 0, 0] := by
  decide +kernel

theorem rows6970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6970 = true := by
  decide +kernel

theorem tot6970 : totK PA10K2 A10K2.t6970 = [0, 0, 386981412979, 1611818084138, 2103556029765, 820997500224, 61654731595, 0, 0, 0] := by
  decide +kernel

theorem rows6971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6971 = true := by
  decide +kernel

theorem tot6971 : totK PA10K2 A10K2.t6971 = [0, 0, 200722185836, 1176457989234, 2122896021229, 1268510798900, 196026653289, 6632180018, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
