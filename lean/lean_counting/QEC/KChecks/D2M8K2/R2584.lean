import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10336 = true := by
  decide +kernel

theorem tot10336 : totK PD2M8K2 D2M8K2.t10336 = [0, 93030726523, 381110173925, 395053111269, 53772113234, 0, 0, 0] := by
  decide +kernel

theorem rows10337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10337 = true := by
  decide +kernel

theorem tot10337 : totK PD2M8K2 D2M8K2.t10337 = [0, 167010734037, 449201943176, 270384163288, 20927213148, 0, 0, 0] := by
  decide +kernel

theorem rows10338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10338 = true := by
  decide +kernel

theorem tot10338 : totK PD2M8K2 D2M8K2.t10338 = [0, 159080229232, 465215124755, 273274367982, 23708406186, 0, 0, 0] := by
  decide +kernel

theorem rows10339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10339 = true := by
  decide +kernel

theorem tot10339 : totK PD2M8K2 D2M8K2.t10339 = [0, 0, 181118904107, 444440715244, 247809270505, 23787324087, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
