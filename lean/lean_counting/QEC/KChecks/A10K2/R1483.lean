import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5932 = true := by
  decide +kernel

theorem tot5932 : totK PA10K2 A10K2.t5932 = [522057398240, 1830091940597, 1950571364590, 701113406956, 78457791152, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5933 = true := by
  decide +kernel

theorem tot5933 : totK PA10K2 A10K2.t5933 = [323642880550, 1500925045388, 2161613924960, 905623473280, 71491573315, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5934 = true := by
  decide +kernel

theorem tot5934 : totK PA10K2 A10K2.t5934 = [0, 562375171880, 2021618762772, 2025830282549, 461729558068, 13816090359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5935 = true := by
  decide +kernel

theorem tot5935 : totK PA10K2 A10K2.t5935 = [0, 410441392527, 1655413459326, 2053228673190, 782725220633, 69329753031, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
