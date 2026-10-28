import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t196 = true := by
  decide +kernel

theorem tot196 : totK PD2M8K2 D2M8K2.t196 = [0, 0, 190572619864, 470026270471, 198898296544, 12206147664, 0, 0] := by
  decide +kernel

theorem rows197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t197 = true := by
  decide +kernel

theorem tot197 : totK PD2M8K2 D2M8K2.t197 = [0, 0, 11978940098, 302802235573, 439649148826, 103005868141, 1369150432, 0] := by
  decide +kernel

theorem rows198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t198 = true := by
  decide +kernel

theorem tot198 : totK PD2M8K2 D2M8K2.t198 = [0, 0, 86403723232, 391112282726, 347400546136, 41032153799, 0, 0] := by
  decide +kernel

theorem rows199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t199 = true := by
  decide +kernel

theorem tot199 : totK PD2M8K2 D2M8K2.t199 = [0, 0, 222427728550, 483484356656, 163405283392, 8337422257, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
