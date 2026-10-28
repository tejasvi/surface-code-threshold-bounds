import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8044 = true := by
  decide +kernel

theorem tot8044 : totK PA10K2 A10K2.t8044 = [0, 0, 0, 286185292359, 1219060111506, 1996723097041, 1310960760328, 231504738720, 6860445330, 0] := by
  decide +kernel

theorem rows8045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8045 = true := by
  decide +kernel

theorem tot8045 : totK PA10K2 A10K2.t8045 = [0, 0, 0, 582309330060, 1941989811875, 1898371071206, 470626188578, 14807273486, 0, 0] := by
  decide +kernel

theorem rows8046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8046 = true := by
  decide +kernel

theorem tot8046 : totK PA10K2 A10K2.t8046 = [0, 0, 0, 0, 746650207877, 2210739598909, 1690597858633, 284632793307, 6853348008, 0] := by
  decide +kernel

theorem rows8047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8047 = true := by
  decide +kernel

theorem tot8047 : totK PA10K2 A10K2.t8047 = [0, 0, 0, 0, 472157759370, 1832757867631, 2075450629517, 604688976829, 23826692321, 0] := by
  decide +kernel

end QECKChecks.A10K2
