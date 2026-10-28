import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5148 = true := by
  decide +kernel

theorem tot5148 : totK PD2M8K2 D2M8K2.t5148 = [0, 0, 198423501610, 478456505330, 225625802718, 12373752831, 0, 0] := by
  decide +kernel

theorem rows5149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5149 = true := by
  decide +kernel

theorem tot5149 : totK PD2M8K2 D2M8K2.t5149 = [0, 0, 48187601698, 323294148173, 430053111030, 86530422807, 1164319620, 0] := by
  decide +kernel

theorem rows5150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5150 = true := by
  decide +kernel

theorem tot5150 : totK PD2M8K2 D2M8K2.t5150 = [0, 0, 0, 203765667111, 474786547920, 188939128469, 11885407614, 0] := by
  decide +kernel

theorem rows5151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5151 = true := by
  decide +kernel

theorem tot5151 : totK PD2M8K2 D2M8K2.t5151 = [0, 0, 170051513913, 443919169775, 259362207514, 29424794885, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
