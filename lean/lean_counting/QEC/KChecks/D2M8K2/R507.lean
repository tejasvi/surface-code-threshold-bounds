import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2028 = true := by
  decide +kernel

theorem tot2028 : totK PD2M8K2 D2M8K2.t2028 = [0, 0, 172836110524, 462043890931, 237246546093, 14245223553, 0, 0] := by
  decide +kernel

theorem rows2029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2029 = true := by
  decide +kernel

theorem tot2029 : totK PD2M8K2 D2M8K2.t2029 = [0, 0, 181992515963, 472810958606, 249864063642, 17424630022, 0, 0] := by
  decide +kernel

theorem rows2030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2030 = true := by
  decide +kernel

theorem tot2030 : totK PD2M8K2 D2M8K2.t2030 = [0, 0, 175567757987, 469046576965, 241263467526, 13354704708, 0, 0] := by
  decide +kernel

theorem rows2031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2031 = true := by
  decide +kernel

theorem tot2031 : totK PD2M8K2 D2M8K2.t2031 = [0, 0, 0, 283749250548, 491673247396, 104010724944, 1171084559, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
