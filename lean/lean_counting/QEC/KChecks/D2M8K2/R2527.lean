import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10108 = true := by
  decide +kernel

theorem tot10108 : totK PD2M8K2 D2M8K2.t10108 = [0, 0, 182626778320, 466787867554, 217577840946, 16849265726, 0, 0] := by
  decide +kernel

theorem rows10109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10109 = true := by
  decide +kernel

theorem tot10109 : totK PD2M8K2 D2M8K2.t10109 = [0, 0, 169656091965, 475433114817, 227178523607, 11015599377, 0, 0] := by
  decide +kernel

theorem rows10110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10110 = true := by
  decide +kernel

theorem tot10110 : totK PD2M8K2 D2M8K2.t10110 = [0, 0, 83973255428, 353578039596, 364416728361, 70166916249, 1239866073, 0] := by
  decide +kernel

theorem rows10111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10111 = true := by
  decide +kernel

theorem tot10111 : totK PD2M8K2 D2M8K2.t10111 = [0, 0, 93391851717, 399393752271, 376449088300, 43004762913, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
