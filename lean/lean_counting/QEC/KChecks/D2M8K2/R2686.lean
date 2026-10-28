import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10744 = true := by
  decide +kernel

theorem tot10744 : totK PD2M8K2 D2M8K2.t10744 = [0, 0, 81743569514, 334943916203, 364237574890, 107319963602, 2554132940, 0] := by
  decide +kernel

theorem rows10745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10745 = true := by
  decide +kernel

theorem tot10745 : totK PD2M8K2 D2M8K2.t10745 = [0, 0, 175070207920, 455039754234, 255690902481, 19833179519, 0, 0] := by
  decide +kernel

theorem rows10746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10746 = true := by
  decide +kernel

theorem tot10746 : totK PD2M8K2 D2M8K2.t10746 = [0, 0, 138955888048, 421858083307, 288035126412, 21330704210, 0, 0] := by
  decide +kernel

theorem rows10747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10747 = true := by
  decide +kernel

theorem tot10747 : totK PD2M8K2 D2M8K2.t10747 = [0, 0, 0, 259475962366, 504035657463, 113690847293, 2109827372, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
