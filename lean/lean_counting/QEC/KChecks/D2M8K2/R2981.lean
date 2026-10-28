import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11924 = true := by
  decide +kernel

theorem tot11924 : totK PD2M8K2 D2M8K2.t11924 = [0, 104314460792, 443158070690, 317757601994, 28460464288, 0, 0, 0] := by
  decide +kernel

theorem rows11925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11925 = true := by
  decide +kernel

theorem tot11925 : totK PD2M8K2 D2M8K2.t11925 = [0, 0, 231136621183, 508811018537, 140896910419, 4031931762, 0, 0] := by
  decide +kernel

theorem rows11926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11926 = true := by
  decide +kernel

theorem tot11926 : totK PD2M8K2 D2M8K2.t11926 = [0, 156475001426, 412591327818, 272181270024, 56693797644, 1186940923, 0, 0] := by
  decide +kernel

theorem rows11927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11927 = true := by
  decide +kernel

theorem tot11927 : totK PD2M8K2 D2M8K2.t11927 = [0, 165896746755, 444725131011, 272829302333, 20950310263, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
