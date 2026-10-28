import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6616 = true := by
  decide +kernel

theorem tot6616 : totK PD2M8K2 D2M8K2.t6616 = [0, 0, 210307884110, 490532409016, 166673234195, 9521435666, 0, 0] := by
  decide +kernel

theorem rows6617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6617 = true := by
  decide +kernel

theorem tot6617 : totK PD2M8K2 D2M8K2.t6617 = [0, 86311067613, 331582716542, 367506462015, 88134595308, 3462014130, 0, 0] := by
  decide +kernel

theorem rows6618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6618 = true := by
  decide +kernel

theorem tot6618 : totK PD2M8K2 D2M8K2.t6618 = [0, 186814910728, 448938498913, 240147747062, 18532771655, 0, 0, 0] := by
  decide +kernel

theorem rows6619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6619 = true := by
  decide +kernel

theorem tot6619 : totK PD2M8K2 D2M8K2.t6619 = [0, 106131590419, 406855457586, 328764868697, 40194206589, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
