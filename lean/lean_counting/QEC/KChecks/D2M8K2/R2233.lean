import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8932 = true := by
  decide +kernel

theorem tot8932 : totK PD2M8K2 D2M8K2.t8932 = [0, 175328002593, 483721782932, 239732717753, 12397777920, 0, 0, 0] := by
  decide +kernel

theorem rows8933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8933 = true := by
  decide +kernel

theorem tot8933 : totK PD2M8K2 D2M8K2.t8933 = [0, 173961799585, 464560824431, 239382365298, 15671754440, 0, 0, 0] := by
  decide +kernel

theorem rows8934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8934 = true := by
  decide +kernel

theorem tot8934 : totK PD2M8K2 D2M8K2.t8934 = [0, 182658487060, 457459263117, 263560109840, 24669294037, 0, 0, 0] := by
  decide +kernel

theorem rows8935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8935 = true := by
  decide +kernel

theorem tot8935 : totK PD2M8K2 D2M8K2.t8935 = [0, 175567757987, 469935747292, 244053030212, 11123899909, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
