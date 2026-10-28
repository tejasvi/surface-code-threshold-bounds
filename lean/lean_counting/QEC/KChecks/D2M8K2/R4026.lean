import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16104 = true := by
  decide +kernel

theorem tot16104 : totK PD2M8K2 D2M8K2.t16104 = [0, 7461122728, 289003126752, 519357119923, 106878634549, 1493059870, 0, 0] := by
  decide +kernel

theorem rows16105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16105 = true := by
  decide +kernel

theorem tot16105 : totK PD2M8K2 D2M8K2.t16105 = [0, 190202871013, 467120126639, 248641743638, 23349548986, 0, 0, 0] := by
  decide +kernel

theorem rows16106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16106 = true := by
  decide +kernel

theorem tot16106 : totK PD2M8K2 D2M8K2.t16106 = [0, 193923417960, 458182697735, 235535931808, 16468539872, 0, 0, 0] := by
  decide +kernel

theorem rows16107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16107 = true := by
  decide +kernel

theorem tot16107 : totK PD2M8K2 D2M8K2.t16107 = [0, 38140235179, 331517271848, 442301154954, 97057562409, 1267860612, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
