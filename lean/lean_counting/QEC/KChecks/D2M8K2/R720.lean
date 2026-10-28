import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2880 = true := by
  decide +kernel

theorem tot2880 : totK PD2M8K2 D2M8K2.t2880 = [0, 223988244846, 494886871561, 165525513363, 4763850746, 0, 0, 0] := by
  decide +kernel

theorem rows2881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2881 = true := by
  decide +kernel

theorem tot2881 : totK PD2M8K2 D2M8K2.t2881 = [0, 180915426010, 455672209985, 229399180769, 17223525822, 0, 0, 0] := by
  decide +kernel

theorem rows2882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2882 = true := by
  decide +kernel

theorem tot2882 : totK PD2M8K2 D2M8K2.t2882 = [0, 202381974910, 466845906471, 192251575381, 9653832318, 0, 0, 0] := by
  decide +kernel

theorem rows2883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2883 = true := by
  decide +kernel

theorem tot2883 : totK PD2M8K2 D2M8K2.t2883 = [0, 103956497021, 413917630923, 317948652084, 29157609761, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
