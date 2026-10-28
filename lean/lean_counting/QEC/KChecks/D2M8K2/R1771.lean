import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7084 = true := by
  decide +kernel

theorem tot7084 : totK PD2M8K2 D2M8K2.t7084 = [0, 146406985473, 444282398712, 283784401202, 22265998931, 0, 0, 0] := by
  decide +kernel

theorem rows7085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7085 = true := by
  decide +kernel

theorem tot7085 : totK PD2M8K2 D2M8K2.t7085 = [0, 0, 275341626515, 502335829218, 110036748202, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7086 = true := by
  decide +kernel

theorem tot7086 : totK PD2M8K2 D2M8K2.t7086 = [0, 143290679590, 418160745636, 337149481020, 40361406276, 0, 0, 0] := by
  decide +kernel

theorem rows7087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7087 = true := by
  decide +kernel

theorem tot7087 : totK PD2M8K2 D2M8K2.t7087 = [0, 204054939145, 476211156139, 211750684322, 12287346641, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
