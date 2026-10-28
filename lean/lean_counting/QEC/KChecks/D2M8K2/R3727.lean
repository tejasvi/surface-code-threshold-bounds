import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14908 = true := by
  decide +kernel

theorem tot14908 : totK PD2M8K2 D2M8K2.t14908 = [0, 177615691747, 474839656371, 253585036007, 20128547347, 0, 0, 0] := by
  decide +kernel

theorem rows14909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14909 = true := by
  decide +kernel

theorem tot14909 : totK PD2M8K2 D2M8K2.t14909 = [0, 181687999219, 474392398896, 239285484674, 12551143345, 0, 0, 0] := by
  decide +kernel

theorem rows14910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14910 = true := by
  decide +kernel

theorem tot14910 : totK PD2M8K2 D2M8K2.t14910 = [0, 0, 297050971032, 490223415824, 103664092076, 1242138600, 0, 0] := by
  decide +kernel

theorem rows14911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14911 = true := by
  decide +kernel

theorem tot14911 : totK PD2M8K2 D2M8K2.t14911 = [0, 0, 213349467412, 472825241215, 167554344501, 7182288656, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
