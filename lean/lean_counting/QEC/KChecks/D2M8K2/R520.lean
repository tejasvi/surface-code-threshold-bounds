import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2080 = true := by
  decide +kernel

theorem tot2080 : totK PD2M8K2 D2M8K2.t2080 = [0, 205673097969, 480416262319, 224317741555, 11687667855, 0, 0, 0] := by
  decide +kernel

theorem rows2081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2081 = true := by
  decide +kernel

theorem tot2081 : totK PD2M8K2 D2M8K2.t2081 = [0, 0, 293448620783, 497754451926, 104809774968, 1164319620, 0, 0] := by
  decide +kernel

theorem rows2082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2082 = true := by
  decide +kernel

theorem tot2082 : totK PD2M8K2 D2M8K2.t2082 = [0, 84940856143, 337392260050, 361462210583, 105798097464, 4234510686, 0, 0] := by
  decide +kernel

theorem rows2083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2083 = true := by
  decide +kernel

theorem tot2083 : totK PD2M8K2 D2M8K2.t2083 = [0, 178906673447, 442208958008, 264295674764, 28217078867, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
