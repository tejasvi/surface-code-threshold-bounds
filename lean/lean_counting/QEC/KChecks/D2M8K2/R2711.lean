import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10844 = true := by
  decide +kernel

theorem tot10844 : totK PD2M8K2 D2M8K2.t10844 = [0, 0, 260439635680, 441534166277, 190993453992, 19862268668, 0, 0] := by
  decide +kernel

theorem rows10845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10845 = true := by
  decide +kernel

theorem tot10845 : totK PD2M8K2 D2M8K2.t10845 = [0, 0, 175419530234, 494421262987, 222805074202, 6917919723, 0, 0] := by
  decide +kernel

theorem rows10846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10846 = true := by
  decide +kernel

theorem tot10846 : totK PD2M8K2 D2M8K2.t10846 = [0, 126949257592, 349491370476, 303466006283, 113646697095, 6800370819, 0, 0] := by
  decide +kernel

theorem rows10847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10847 = true := by
  decide +kernel

theorem tot10847 : totK PD2M8K2 D2M8K2.t10847 = [0, 173146608690, 435987689789, 270734980553, 29877160257, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
