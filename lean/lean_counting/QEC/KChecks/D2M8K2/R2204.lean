import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8816 = true := by
  decide +kernel

theorem tot8816 : totK PD2M8K2 D2M8K2.t8816 = [0, 172675080252, 450760848217, 267915690000, 35724218690, 0, 0, 0] := by
  decide +kernel

theorem rows8817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8817 = true := by
  decide +kernel

theorem tot8817 : totK PD2M8K2 D2M8K2.t8817 = [0, 174324890571, 446664493527, 257067111460, 22128158425, 0, 0, 0] := by
  decide +kernel

theorem rows8818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8818 = true := by
  decide +kernel

theorem tot8818 : totK PD2M8K2 D2M8K2.t8818 = [0, 93768764846, 392516349995, 364423405944, 57945266117, 1249641317, 0, 0] := by
  decide +kernel

theorem rows8819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8819 = true := by
  decide +kernel

theorem tot8819 : totK PD2M8K2 D2M8K2.t8819 = [0, 0, 230409410080, 496157496835, 158159315003, 3660139582, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
