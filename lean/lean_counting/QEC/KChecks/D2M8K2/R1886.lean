import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7544 = true := by
  decide +kernel

theorem tot7544 : totK PD2M8K2 D2M8K2.t7544 = [0, 33367265142, 34929308419, 198194761503, 449490223967, 167232334729, 5510671013, 0] := by
  decide +kernel

theorem rows7545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7545 = true := by
  decide +kernel

theorem tot7545 : totK PD2M8K2 D2M8K2.t7545 = [0, 194253533482, 489011426269, 207091744171, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows7546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7546 = true := by
  decide +kernel

theorem tot7546 : totK PD2M8K2 D2M8K2.t7546 = [0, 189161375557, 465008416319, 215939664858, 10294279025, 0, 0, 0] := by
  decide +kernel

theorem rows7547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7547 = true := by
  decide +kernel

theorem tot7547 : totK PD2M8K2 D2M8K2.t7547 = [0, 0, 279415582037, 501574571722, 108244782008, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
