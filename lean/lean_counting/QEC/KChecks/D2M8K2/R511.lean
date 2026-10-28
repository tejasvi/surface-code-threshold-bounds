import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2044 = true := by
  decide +kernel

theorem tot2044 : totK PD2M8K2 D2M8K2.t2044 = [0, 116562474709, 430769340928, 324652206613, 36293670446, 0, 0, 0] := by
  decide +kernel

theorem rows2045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2045 = true := by
  decide +kernel

theorem tot2045 : totK PD2M8K2 D2M8K2.t2045 = [0, 0, 152242184526, 442611548090, 274474357608, 25566528197, 0, 0] := by
  decide +kernel

theorem rows2046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2046 = true := by
  decide +kernel

theorem tot2046 : totK PD2M8K2 D2M8K2.t2046 = [0, 56870875374, 220673392785, 407004842919, 201305639159, 7892383752, 0, 0] := by
  decide +kernel

theorem rows2047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2047 = true := by
  decide +kernel

theorem tot2047 : totK PD2M8K2 D2M8K2.t2047 = [0, 181763419837, 494539603221, 221703927005, 5117551749, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
