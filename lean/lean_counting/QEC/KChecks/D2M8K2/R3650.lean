import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14600 = true := by
  decide +kernel

theorem tot14600 : totK PD2M8K2 D2M8K2.t14600 = [0, 87765346930, 378697172551, 361625488572, 69204612909, 1369150432, 0, 0] := by
  decide +kernel

theorem rows14601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14601 = true := by
  decide +kernel

theorem tot14601 : totK PD2M8K2 D2M8K2.t14601 = [0, 0, 311008914501, 511193952357, 73713221081, 0, 0, 0] := by
  decide +kernel

theorem rows14602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14602 = true := by
  decide +kernel

theorem tot14602 : totK PD2M8K2 D2M8K2.t14602 = [0, 173477795397, 459140258732, 244599447931, 19875466017, 0, 0, 0] := by
  decide +kernel

theorem rows14603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14603 = true := by
  decide +kernel

theorem tot14603 : totK PD2M8K2 D2M8K2.t14603 = [0, 151445164458, 446471784885, 274675977619, 20245468575, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
