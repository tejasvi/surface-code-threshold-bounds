import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15888 = true := by
  decide +kernel

theorem tot15888 : totK PD2M8K2 D2M8K2.t15888 = [0, 152989216845, 469871898658, 245978698247, 15936446759, 0, 0, 0] := by
  decide +kernel

theorem rows15889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15889 = true := by
  decide +kernel

theorem tot15889 : totK PD2M8K2 D2M8K2.t15889 = [0, 153142458884, 444981005451, 266296570392, 18252364079, 0, 0, 0] := by
  decide +kernel

theorem rows15890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15890 = true := by
  decide +kernel

theorem tot15890 : totK PD2M8K2 D2M8K2.t15890 = [0, 0, 273935055544, 503830815861, 105082585819, 1369150432, 0, 0] := by
  decide +kernel

theorem rows15891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15891 = true := by
  decide +kernel

theorem tot15891 : totK PD2M8K2 D2M8K2.t15891 = [0, 162074439460, 418747927479, 315767436889, 35624617202, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
