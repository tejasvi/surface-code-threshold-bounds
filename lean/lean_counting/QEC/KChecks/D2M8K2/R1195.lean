import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4780 = true := by
  decide +kernel

theorem tot4780 : totK PD2M8K2 D2M8K2.t4780 = [0, 0, 200597338492, 481704220475, 194623725173, 6645949705, 0, 0] := by
  decide +kernel

theorem rows4781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4781 = true := by
  decide +kernel

theorem tot4781 : totK PD2M8K2 D2M8K2.t4781 = [0, 0, 181978772450, 469729267036, 246752436859, 18333014298, 0, 0] := by
  decide +kernel

theorem rows4782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4782 = true := by
  decide +kernel

theorem tot4782 : totK PD2M8K2 D2M8K2.t4782 = [0, 0, 206769707256, 476036073128, 197283238466, 7689860642, 0, 0] := by
  decide +kernel

theorem rows4783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4783 = true := by
  decide +kernel

theorem tot4783 : totK PD2M8K2 D2M8K2.t4783 = [0, 0, 170654483899, 462570669485, 237190321033, 16936124968, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
