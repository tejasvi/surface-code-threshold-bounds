import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15812 = true := by
  decide +kernel

theorem tot15812 : totK PD2M8K2 D2M8K2.t15812 = [0, 178599777073, 431286502766, 268407228518, 54506132967, 7093008096, 0, 0] := by
  decide +kernel

theorem rows15813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15813 = true := by
  decide +kernel

theorem tot15813 : totK PD2M8K2 D2M8K2.t15813 = [0, 174958660482, 472525554905, 241295343170, 11429545154, 0, 0, 0] := by
  decide +kernel

theorem rows15814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15814 = true := by
  decide +kernel

theorem tot15814 : totK PD2M8K2 D2M8K2.t15814 = [0, 89061927447, 323520779725, 360834668873, 135800803641, 15864095392, 0, 0] := by
  decide +kernel

theorem rows15815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15815 = true := by
  decide +kernel

theorem tot15815 : totK PD2M8K2 D2M8K2.t15815 = [0, 0, 184599414286, 461519652518, 235241633098, 13530797253, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
