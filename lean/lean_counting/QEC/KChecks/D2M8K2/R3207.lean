import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12828 = true := by
  decide +kernel

theorem tot12828 : totK PD2M8K2 D2M8K2.t12828 = [0, 162037142227, 465961585529, 267785742748, 25691313426, 0, 0, 0] := by
  decide +kernel

theorem rows12829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12829 = true := by
  decide +kernel

theorem tot12829 : totK PD2M8K2 D2M8K2.t12829 = [0, 0, 174866789798, 446218908216, 252984041627, 25370006417, 0, 0] := by
  decide +kernel

theorem rows12830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12830 = true := by
  decide +kernel

theorem tot12830 : totK PD2M8K2 D2M8K2.t12830 = [0, 0, 199891928582, 500040431166, 201268807753, 5430665091, 0, 0] := by
  decide +kernel

theorem rows12831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12831 = true := by
  decide +kernel

theorem tot12831 : totK PD2M8K2 D2M8K2.t12831 = [0, 166517582303, 387917552870, 238851047364, 102792231786, 6801036714, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
